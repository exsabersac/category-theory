(**
* Boundary probes for the power-set universal element

    Companion to Instance/Sets/Powerset/Universal.v,
    Instance/FinSet/Powerset.v and Structure/SubobjectClassifier/Natural.v
    (issue #311; Mac Lane §III.1 Exercise 2, Riehl §2.3 Example 2.3.6,
    Awodey §5.3 Example 5.14).  Those files make strength claims whose
    negative side is a universe wall or a typing boundary; a measurement
    made outside the tree would not be noticed by a refactor, so it is
    pinned here.  **If the [Fail] commands below stop failing, this file
    breaks the build.**

    Each negative is paired with a positive control that must SUCCEED, for
    the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone passes
    just as happily when a name has been renamed out from under it.  The
    instrument itself was checked — wrapping [Fail] around a succeeding
    command reports "The command has not failed!" and aborts compilation —
    and each negative was compiled once with the [Fail] stripped, to
    confirm the error is the intended one and not a syntax, scope or
    resolution error.  The import list below is the union of the two target
    files' own import lists, in their order — of the THREE target files, less
    [Category.Structure.Topos] and [Category.Instance.FinSet.Topos], which
    arrive transitively via [Instance.FinSet.Powerset] — for the reason
    Instance/Field/Frac.v's probe header records: a shortened prefix can
    turn a negative into a FALSE PASS by removing the coercion or instance
    that would otherwise make the command elaborate.

    Two further POSITIVE controls are carried that no negative demands,
    because a single control can make an impossibility read wider than it
    is.  [Section YonedaIsUsableElsewhere] elaborates the very constant
    that [Sets] refuses, at a category whose three universes can be
    identified — so boundary (1) is a fact about [Sets] and not about the
    constant.  [Section PowersetAtTwoSizes] instantiates the contravariant
    power-set functor and its universal element at two DIFFERENT declared
    universe pairs, one immediately above [Set] and one two levels higher,
    so "available at one level" is not read off a single instantiation.

    THE FIVE BOUNDARIES.
    CORRECTION (#1347): four now, (5) having become a control.

    (1) THE YONEDA ROUTE IS UNAVAILABLE AT [Sets].
    Theory/Universal/Element.v records that [Yoneda_Lemma], and hence
    [representability_by_yoneda], [universal_element_yoneda] and
    [universal_element_representation], are stated over a category whose
    object, hom and proof universes are IDENTIFIED.  [Sets@{o so}] is
    [Category@{so o o}] with [o < so] forced, so the identification cannot
    be made and the refusal is a genuine universe inconsistency ("Cannot
    enforce _ = _ because _ < _", naming the two anonymous levels).  The
    positive control is the Yoneda-FREE route at exactly the same
    arguments, which is what the target file uses.

    (2) THE UNIVERSAL ELEMENT IS NOT THE POINT.  Riehl's emphasis, as a
    typing boundary in both settings: over [Sets] the point ⊤ is a
    [carrier Powerset_Omega] and the element is a
    [carrier (Powerset_Prop_obj Powerset_Omega)]; over [FinSet] the point
    is a [Fin.t 2] and the element a [Fin.t 4].  Putting the point where
    the element belongs is a type error, and the controls are the two
    universal elements themselves.

    (3) THE ROUND TRIP IS [≈] AND NOT [eq_refl] OVER [Sets].  Pulling {⊤}
    back along the characteristic map of S returns S only up to pointwise
    mutual implication: the two [SetoidMorphism] records carry different
    respectfulness proofs, and the predicate itself has acquired a
    [Powerset_squash].  Over [FinSet] the corresponding round trip IS
    Leibniz — [fin_tabulate_apply] — which is the difference between the
    two files, so that Leibniz statement is the control.

    (4) THE TWO READINGS OF {⊤} AGREE ONLY UP TO [≈].  [Powerset_holds] is
    the predicate "P holds"; [Powerset_truth_subset] is the donor's
    truncated singleton at ⊤.  They are pointwise interderivable and are
    not the same term.

    (5) THE FUNCTOR LAWS OF [Powerset_Prop_op] ARE NOT DEFINITIONAL.  The
    inverse image along the identity is the subset again as a PREDICATE,
    on the nose, but not as a record: the rebuilt [proper_morphism] field
    differs.  The control is the [≈] form the functor is actually built
    from.
    CORRECTION (#1347): the identity law now holds at [eq_refl], since
    Instance/Sets.v gives its identity's and composite's properness fields
    as terms, and the command below is a control; so does the composition
    law, which [powerset_fmap_comp_strict] below pins (in a copy of this
    file as it stood at master 687ac356, compiled against that tree, that
    command is refused with "cannot unify").  The
    cause above, the rebuilt field differing, was argued; the measurement
    shows the residue was the standard library's, the opaque lemmas
    instance resolution had put in those two fields.

--------
* 幂集通用元素的边界探针

《Instance/Sets/Powerset/Universal.v》、《Instance/FinSet/Powerset.v》和《Structure/SubobjectClassifier/Natural.v》的配套文件（问题 #311；Mac Lane 第 III.1 节练习 2，Riehl 第 2.3 节例 2.3.6，Awodey 第 5.3 节例 5.14）。这些文件提出了强度声明，其负面方面是宇宙墙或类型边界；在树之外进行的测量不会被重构注意到，因此固定在这里。**如果下面的 [Fail] 命令不再失败，这个文件将导致构建失败。**

每个负样本都与必须成功的正控制配对，其原因如 Test/ProbeQuiverConstructions.v 所示：仅使用 [Fail] 即使在其下的名称已被重命名时也会正常通过。该工具本身已被检查——将 [Fail] 包裹在成功的命令周围会报告“命令未失败！”并中止编译——每个负样本也都在去掉 [Fail] 后编译过一次，以确认错误是预期的，而不是语法、作用域或解析错误。下面的导入列表是两个目标文件自身导入列表的并集，按它们的顺序排列——在三个目标文件中，去掉了通过 [Instance.FinSet.Powerset] 间接导入的 [Category.Structure.Topos] 和 [Category.Instance.FinSet.Topos]——原因如 Instance/Field/Frac.v 的探针头记录：缩短的前缀可能通过删除本来会使命令展开的强制类型或实例，将一个负样本变为假通过。

进一步进行了两个正向控制，而没有负向要求，因为单一控制可能使不可能的读数比实际更宽。[Section YonedaIsUsableElsewhere] 详细说明了 [Sets] 拒绝的常量，在一个其三个宇宙可以识别的类别中 —— 因此边界（1）是关于 [Sets] 的事实，而不是关于常量的事实。[Section PowersetAtTwoSizes] 在两个不同声明的宇宙对上实例化了逆变幂集函子及其普遍元素，一个在 [Set] 之上紧接的一层，另一个在两层之上，因此“在一个层级可用”不能从单一实例中得出。

五个界限。
    更正（#1347）：现在是四个，（第五个）已成为一种控制。

(1) YONEDA 路径在 [Sets] 上不可用。Theory/Universal/Element.v 记录了 [Yoneda_Lemma]，因此 [representability_by_yoneda]、[universal_element_yoneda] 和 [universal_element_representation] 声明在一个对象、Hom 和证明宇宙被识别的范畴上。[Sets@{o so}] 是 [Category@{so o o}] 强制 [o < so] 后的结果，因此无法进行识别，拒绝是一个真正的宇宙不一致（“无法强制 _ = _ 因为 _ < _”，指明了两个匿名层级）。正向控制是在完全相同参数下的 Yoneda-FREE 路径，这也是目标文件使用的方式。

(2) 普遍元素并不是重点。Riehl 的强调，在两种环境中的类型边界：在 [Sets] 上，点 ⊤ 是一个 [carrier Powerset_Omega]，而元素是一个 [carrier (Powerset_Prop_obj Powerset_Omega)]；在 [FinSet] 上，点是一个 [Fin.t 2]，元素是一个 [Fin.t 4]。把点放到元素所在的位置是一个类型错误，而控制就是两个普遍元素本身。

(3) 往返行程是 [≈] 而不是 [eq_refl] 经过 [Sets]。沿着 S 的特征映射拉回 {⊤} 只会返回 S，且仅在逐点相互蕴涵下有效：这两个 [SetoidMorphism] 记录包含不同的尊重性证明，并且谓词本身已经获得了一个 [Powerset_squash]。在 [FinSet] 上，相应的往返行程是 Leibniz — [fin_tabulate_apply] — 这就是两个文件之间的区别，因此 Leibniz 陈述是控制。

(4) {⊤} 的两种读法仅在 [≈] 上一致。[Powerset_holds] 是谓词“P 成立”；[Powerset_truth_subset] 是捐赠者在 ⊤ 上的截断单集。它们在每一点上都可以互相推导，但不是同一项。

(5) [Powerset_Prop_op] 的函子定律不是定义性的。沿着恒等映射的逆像作为谓词再次是子集，严格来说是这样，但作为记录则不是：重建的 [proper_morphism] 字段有所不同。控制来自于构建该函子的 [≈] 形式。

修正（#1347）：现在在 [eq_refl] 上恒等律成立，因为 Instance/Sets.v 给出了其恒等和复合的 properness 字段作为项，而下面的命令是一个控制；组合律也是如此，下面 [powerset_fmap_comp_strict] 固定了（在本文件的一个副本中，基于 master 687ac356，在该树上编译，该命令会因“无法统一”而被拒绝）。上述原因，即重建字段的不同，已经讨论过；测量显示残余部分是标准库的，实例解析所放入那两个字段的不透明引理。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** (1) The Yoneda route at [Sets] / ** (1) [Sets]上的Yoneda路线 *)

(*
NEGATIVE.  Stripped, this reports a universe inconsistency between the
   object universe of [Sets] and its hom universe.

--------
否定。剥离后，这报告了 [Sets] 的对象宇宙与其同源宇宙之间的不一致。
*)
Fail Check @universal_element_yoneda (Sets^op) Powerset_Prop_op Powerset_Omega.

(* NEGATIVE, the composed form. / 消极的，组成形式。 *)
Fail Check
  @universal_element_representation (Sets^op) Powerset_Prop_op Powerset_Omega.

(* POSITIVE CONTROL: the Yoneda-free route at the same three arguments. / 阳性对照：在相同三个自变量下的 Yoneda 自由路径。 *)
Check ue_representation Powerset_Prop_op Powerset_Omega
        Powerset_Prop_universal_element.

(* POSITIVE CONTROL: and the whole representation the target file builds. / 阳性对照：以及目标文件构建的整个表示。 *)
Check Powerset_representation.

(*
POSITIVE CONTROL AT A DIFFERENT CATEGORY, so that the negative above is
   not read as "this donor constant is unusable".  Over a category whose
   object, hom and proof universes CAN be identified, the same constant
   elaborates; the refusal is a fact about [Sets], not about
   [universal_element_yoneda].

--------
在不同类别上的阳性对照，这样上面的阴性就不会被解读为“这个给定常数不可用”。在一个其对象、同态和证明范畴可被识别的类别上，同一常数会被展开；拒绝是关于 [Sets] 的事实，而不是关于 [universal_element_yoneda] 的事实。
*)
Section YonedaIsUsableElsewhere.
  Universe u.
  Context (K : Category@{u u u}) (F : K ⟶ Sets) (r : K).
  Check @universal_element_yoneda K F r.
End YonedaIsUsableElsewhere.

(*
POSITIVE CONTROLS AT TWO DIFFERENT SIZES, so that "the contravariant
   power-set functor is available at one level" is not read off a single
   instantiation.  [Powerset_Prop_truth] forces [Set < o], so the smaller
   of the two sits immediately above [Set].

--------
在两个不同的尺寸上进行阳性对照，以便“逆变幂集函子在某一层可用”不会仅从单一实例中读取。[Powerset_Prop_truth] 强制 [Set < o]，因此两者中较小的紧挨着 [Set] 上方。
*)
Section PowersetAtTwoSizes.
  Universe u1 u2 u3 u4.
  Constraint Set < u1.
  Constraint u1 < u2.
  Constraint u2 < u3.
  Constraint u3 < u4.
  Check Powerset_Prop_op@{u1 u2}.
  Check Powerset_Prop_op@{u3 u4}.
  Check Powerset_Prop_universal_element@{u1 u2}.
  Check Powerset_Prop_universal_element@{u3 u4}.
End PowersetAtTwoSizes.

(* ------------------------------------------------------------------------ *)
(** ** (2) The element is not the point / ** (2) 元素不是重点 *)

(*
NEGATIVE, over [Sets].  Stripped: "The term Powerset_truth_point has type
   carrier Powerset_Omega while it is expected to have type ...".

--------
负面，关于 [Sets]。 去掉："术语 Powerset_truth_point 的类型是 carrier Powerset_Omega，而预期的类型是 ..."。
*)
Fail Example point_is_not_an_element :
  carrier (Powerset_Prop_obj Powerset_Omega) := Powerset_truth_point.

(* POSITIVE CONTROL. / 阳性对照。 *)
Example subset_is_an_element :
  carrier (Powerset_Prop_obj Powerset_Omega) := Powerset_truth_subset.

(* NEGATIVE, over [FinSet]: [Fin.t 2] is not [Fin.t 4]. / 否定，关于 [FinSet]：[Fin.t 2] 不是 [Fin.t 4]。 *)
Fail Example fin_point_is_not_an_element :
  Fin.t (finpow 2) := finpow_truth_point.

(* POSITIVE CONTROL. / 阳性对照。 *)
Example fin_subset_is_an_element :
  Fin.t (finpow 2) := finpow_truth_subset.

(* ------------------------------------------------------------------------ *)
(** ** (3) The [Sets] round trip is [≈] only; the [FinSet] one is Leibniz / ** (3) [Sets] 往返只适用于 [≈]；[FinSet] 的则是莱布尼茨 *)

(*
NEGATIVE.  Stripped: "cannot unify
   Powerset_preimage_of_truth (Powerset_char S) and S".

--------
否定。剥离："无法统一 Powerset_preimage_of_truth (Powerset_char S) 和 S"。
*)
Fail Example sets_round_trip_strict
  (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) :
  Powerset_preimage_of_truth (Powerset_char S) = S := eq_refl.

(* POSITIVE CONTROL: the [≈] form, which is what the target proves. / 阳性对照：[≈] 形式，即目标所证明的形式。 *)
Check (fun (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) =>
         powerset_preimage_char S
         : Powerset_preimage_of_truth (Powerset_char S) ≈ S).

(*
POSITIVE CONTROL, and the CONTRAST: over [FinSet] the same round trip is
   a Leibniz equation, with no setoid step anywhere.

--------
阳性对照，以及对比：在 [FinSet] 上，同样的往返是一个莱布尼茨方程，没有任何集合论步骤。
*)
Check (fun (n : nat) (S : Fin.t (finpow n)) =>
         fin_tabulate_apply S : fin_tabulate (fin_apply S) = S).

(* ------------------------------------------------------------------------ *)
(** ** (4) The two readings of {⊤} / ** (4) {⊤} 的两种读法 *)

(*
NEGATIVE.  Stripped: "cannot unify Powerset_truth_subset and
   Powerset_holds".

--------
否定。被剥离："无法统一 Powerset_truth_subset 和 Powerset_holds"。
*)
Fail Example truth_readings_strict :
  Powerset_truth_subset = Powerset_holds := eq_refl.

(* POSITIVE CONTROL. / 阳性对照。 *)
Check (powerset_truth_subset_holds
       : Powerset_truth_subset ≈ Powerset_holds).

(* ------------------------------------------------------------------------ *)
(** ** (5) The functor laws are not definitional / ** (5) 函子定律不是定义上的 *)

(*
NEGATIVE.  Stripped: "cannot unify fmap[Powerset_Prop_op] id{Sets^op} and
   id{Sets}".  CORRECTION (#1347): a POSITIVE CONTROL now; the command
   holds at [eq_refl].

--------
否定。剥离："无法统一 fmap[Powerset_Prop_op] id{Sets^op} 和 id{Sets}"。修正 (#1347)：现在是一个正控制；命令在 [eq_refl] 上成立。
*)
Example powerset_fmap_id_strict (X : SetoidObject) :
  fmap[Powerset_Prop_op] (id{Sets^op} : X ~{Sets^op}~> X) = id{Sets}
  := eq_refl.

(* POSITIVE CONTROL (#1347): the composition law at [eq_refl] as well. / 阳性对照 (#1347)：在 [eq_refl] 的组成规律也是如此。 *)
Example powerset_fmap_comp_strict (X Y Z : SetoidObject)
  (f : X ~{Sets^op}~> Y) (g : Y ~{Sets^op}~> Z) :
  fmap[Powerset_Prop_op] (g ∘ f)
    = fmap[Powerset_Prop_op] g ∘ fmap[Powerset_Prop_op] f := eq_refl.

(* POSITIVE CONTROL: the [≈] form. / 阳性对照：[≈] 表格。 *)
Check (fun X : SetoidObject => @Powerset_Prop_comap_id X).

(*
POSITIVE CONTROL, and the CONTRAST once more: over [FinSet] the identity
   law of the same functor IS a Leibniz equation on codes.

--------
正控制，以及再次对比：在 [FinSet] 上，同一函子的恒等律是关于代码的莱布尼茨方程。
*)
Check (fun (n : nat) (S : Fin.t (finpow n)) =>
         finpow_map_id S : finpow_map (fun i : Fin.t n => i) S = S).

(* ------------------------------------------------------------------------ *)
(** ** Positive controls that are strength claims in their own right / ** 本身就是力量声明的阳性对照 *)

(*
Over [Sets] a subset IS a map into Ω, at Leibniz equality of TYPES.  This
   is the identification the target file's universal property rests on, and
   it is why that file's content is the single equivalence of (4) rather
   than a bijection between two different things.

--------
在 [Sets] 上，一个子集是映射到 Ω 的映射，在类型的莱布尼茨等价下。这是目标文件的泛性质所依赖的标识，也是为什么该文件的内容是（4）的单一等价而不是两个不同事物之间的双射。
*)
Example sets_subsets_are_maps (A : SetoidObject) :
  carrier (Powerset_Prop_obj A) = (A ~{Sets}~> Powerset_Omega) := eq_refl.

(*
Over [FinSet] the analogous statement is FALSE as a type equation — the
   power set is a [Fin.t (2 ^ n)] and a characteristic map is a function —
   and that is the whole reason the [FinSet] file's correspondence has
   content.  Stripped: a genuine type error.

--------
在 [FinSet] 上，相应的陈述作为类型方程是错误的——幂集是一个 [Fin.t (2 ^ n)]，而特征映射是一个函数——这就是 [FinSet] 文件对应内容存在的全部原因。简化来说：一个真正的类型错误。
*)
Fail Example fin_subsets_are_maps (n : nat) :
  Fin.t (finpow n) = (Fin.t n → Fin.t 2) := eq_refl.

(*
The classifier of [FinSet] and the power-set functor built over it share
   their truth-value object, on the nose.

--------
[FinSet] 的分类器和在其上构建的幂集函子恰好共享它们的真值对象。
*)
Example finset_omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.
