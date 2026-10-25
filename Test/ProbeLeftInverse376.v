Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Skeleton.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Theory.Shapes.
Require Import Category.Adjunction.LeftInverse.

Generalizable All Variables.

(**
* Boundary probes for Adjunction/LeftInverse.v (Mac Lane SS IV.4)

    Each [Fail] below was stripped ONE AT A TIME -- the others left in
    place -- the file recompiled, and the whole error message read, so
    that the KIND of every rejection is measured rather than guessed.
    The kinds are kept lexically apart:

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and no universe
                   clause;
      CONVERSION   two terms of ONE type that do not convert
                   ("Unable to unify" / "cannot unify");
      FORMABILITY  "universe inconsistency: Cannot enforce ...".

    Every constant a negative names also appears OUTSIDE a [Fail], so a
    rename cannot leave a guard vacuously green.  The negatives that
    compare terms compare TERMS OF A FIXED TYPE (an [eq] between two
    explicitly typed sides, or a [Check] of a proposition), never an
    ascription of a term to a type where a coercion -- Coq's
    [reverse_coercion] in particular -- could silently repair the
    mismatch and turn the guard into a false pass.

--------
* Adjunction/LeftInverse.v 的边界探针（Mac Lane SS IV.4）

下面的每个 [Fail] 都是一次去掉一个 —— 其他的保持不变 —— 文件重新编译，然后读取完整的错误信息，这样每个拒绝的类型可以被测量而不是猜测。这些类型在词汇上是分开的：

输入       一个简单的“具有类型 ...，而预期具有类型 ...”，没有“无法统一”也没有宇宙条款；
转换       两个属于同一类型但无法转换的项（“无法统一”/“不能统一”）；
可形成性  “宇宙不一致：无法强制执行 ...”。

每个常量的负名称也出现在 [Fail] 之外，因此重命名不能让保护徒然显示为绿色。比较项的负值比较的是固定类型的项（在两个明确类型的变量之间的 [eq]，或一个命题的 [Check]），而不是将某个项归属到类型上，在这种情况下，强制转换——尤其是 Coq 的 [reverse_coercion]——可能会悄悄修复不匹配，并将保护变成错误通过。
*)

(** ** Instrument check: [Fail] itself must be able to fail. / ** 仪器检查：[Fail] 本身必须能够失败。 *)

Fail Check probe376_no_such_constant_anywhere.

(** ** Controls: the names the negatives below depend on. / ** 控制：下面否定形式所依赖的名称。 *)

Check @LeftAdjointLeftInverse.
Check @lali_characterization.
Check @LeftAdjointFFInjective.
Check @ReflectiveIsoPresentation.
Check @ri_lali_implies_lali.
Check @ri_sub.
Check @lali_implies_ri.
Check @lali_image_insertion.
Check @lali_cycle.
Check @lali_obj.
Check @lali_counit.
Check @LaliImageSub.
Check @ImageTo.
Check @ImageFrom.
Check @image_to_from_obj.
Check @lali_implies_ffi.
Check @ffi_left.
Check @lali_left.
Check @PointAt.
Check @terminal_LALI.
Check @Point.
Check @Incl.
Check @Reflective.
Check @reflective_adj.
Check @reflector.
Check @reflective_counit_iso.
Check @counit.
Check @id_cast.
Check @Functor_StrictEq_Setoid.
Check @lali_along_right_strict.
Check @ffi_implies_ri.
Check @Sub.
Check @Isomorphism.
Check StrictCat.

(**
** 1. TYPING: "the counit is the identity" is not a well-typed
       equation.

    For an arbitrary adjunction the counit at [a] runs [F (G a) ~> a],
    while [id[a]] runs [a ~> a]; the two are the same hom-set only when
    [F (G a)] and [a] are the same object at LEIBNIZ equality.  This is
    exactly why [LeftAdjointLeftInverse] carries the object equation as
    DATA and compares the counit with the identity transported along it,
    and why the issue's suggested "counit ~ nat_id" reading is not
    statable.  The control is the [id_cast] form actually used.

--------
** 1. 输入："the counit is the identity" 不是一个类型良好的方程。

对于任意伴随，[a] 处的余单位运行 [F (G a) ~> a]，而 [id[a] 运行 [a ~> a]；当 [F (G a)] 和 [a] 在 莱布尼茨 等式下是相同对象时，这两个才是相同的同态集。这正是为什么 [LeftAdjointLeftInverse] 将对象方程作为数据携带，并将余单位与沿其传送的恒等进行比较，以及为什么问题中建议的“counit ~ nat_id”读法无法陈述。实际使用的控制是 [id_cast] 形式。
*)

Section CounitIsNotIdentity.

Context {A X : Category}.
Context {F : X ⟶ A}.
Context {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (a : A).

Fail Check (@counit A X F G Adj a ≈ id[a]).

Context (P : LeftAdjointLeftInverse G).

Check (@counit A X (lali_left P) G (lali_adj P) a ≈ id_cast (lali_obj P a)).
Check (lali_counit P a).

End CounitIsNotIdentity.

(**
** 2. TYPING: the same failure at a reflection, which is why clause
       (c) alone does not give clause (a).

    The counit of a reflection runs [reflector R (Incl y) ~> y] and is an
    ISOMORPHISM ([reflective_counit_iso], the control), never an identity:
    a reflector need not fix the objects of the subcategory on the nose.
    Mac Lane re-chooses the reflector on Y by a case distinction on
    membership; here membership [sobj] is proof-relevant, a reflector
    fixing the subcategory on the nose forces membership-proof
    uniqueness, and the unconditional passage is refutable (the target's
    header records the out-of-tree countermodel), so
    [ri_lali_implies_lali] takes the corrected reflector as an explicit
    hypothesis.

--------
** 2. 输入：在反射上出现相同的失败，这就是为什么单独的条款(c)不能得出条款(a)的原因。

反射的余单位运行 [reflector R (Incl y) ~> y] 并且是一个同构 ([reflective_counit_iso]，控制)，而绝不是恒等的：反射器不必严格固定子类别的对象。Mac Lane 通过对成员资格进行情况区分重新选择了 Y 上的反射器；这里成员资格 [sobj] 是与证明相关的，一个严格固定子类别的反射器会强制成员资格证明的唯一性，而无条件的推导是可反驳的（目标的标题记录了树外的反例），因此 [ri_lali_implies_lali] 将经过修正的反射器作为显式假设。
*)

Section ReflectionCounit.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (y : Sub C S).

Fail Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
              ≈ id[y]).

Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
         ≈ to (reflective_counit_iso R y)).

End ReflectionCounit.

(**
** 3. TYPING: the third leg is CONDITIONAL, and the unconditional
       form is not what is proved.

    [ri_lali_implies_lali] wants the presentation AND a
    left-adjoint-left-inverse of the insertion; applied to the
    presentation alone it is still a function, so the ascription is
    rejected.  The control supplies the second argument.

--------
** 3. 输入：第三部分是条件的，而无条件形式并不是所证明的内容。

[ri_lali_implies_lali] 想要的是演示以及插入的左伴随左逆；单独应用于演示，它仍然是一个函数，所以赋值被拒绝。控制提供了第二个参数。
*)

Section ThirdLegIsConditional.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (Pres : ReflectiveIsoPresentation G).
Context (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))).

Fail Definition unconditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres.

Definition conditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres L.

End ThirdLegIsConditional.

(**
** 4. CONVERSION: going round the cycle does not return the datum.

    [lali_cycle] rebuilds the adjunction through the image subcategory,
    so its left adjoint is [ImageFrom o ImageTo o F] and its transposes
    are rebuilt; the two sides are terms of ONE type that do not
    convert.  The controls are the two identifications that DO hold on
    the nose.

--------
** 4. 转换：绕着循环进行并不会返回数据。

[lali_cycle] 通过像子范畴重建伴随，因此它的左伴随是 [ImageFrom o ImageTo o F]，其转置也会被重建；两边是同一类型的项，但不会转换。控制是两个在本质上确实成立的同一性。
*)

Section CycleIsNotIdentity.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Fail Example cycle_is_identity : lali_cycle P = P := eq_refl.

Example ffi_left_strict : ffi_left (lali_implies_ffi P) = lali_left P :=
  eq_refl.

Example ri_sub_strict : ri_sub (lali_implies_ri P) = @LaliImageSub A X G :=
  eq_refl.

End CycleIsNotIdentity.

(**
** 5. CONVERSION: the [ImageTo o ImageFrom] object equality is not
       [eq_refl] at a variable object.

    It is built by eliminating the membership witness, so it reduces only
    once that witness is a constructor -- which is what the control at an
    object in the image of [ImageTo] exhibits.

--------
** 5. 转换：[ImageTo o ImageFrom] 对象的相等性在变量对象上并不等于 [eq_refl]。

它是通过消除成员资格见证构建的，因此只有当该见证是构造函数时才会减少一次——这正是 [ImageTo] 映像中的对象上显示的控制所体现的。
*)

Section ImageRoundTripObj.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (B : LeftAdjointFFInjective G).
Context (y : Sub X (@LaliImageSub A X G)).
Context (a : A).

Fail Example image_obj_refl : image_to_from_obj B y = eq_refl := eq_refl.

Example image_obj_refl_at_image :
  image_to_from_obj B (@ImageTo A X G a) = eq_refl := eq_refl.

End ImageRoundTripObj.

(**
** 6. FORMABILITY: a strict functor equality identifies the two
       categories' hom-and-proof universes.

    [Functor_StrictEq_Setoid] (Theory/Functor.v) is declared over
    [Category@{u1 u4 u4}] and [Category@{u2 u4 u4}] -- ONE hom level for
    source and target -- so every statement below that mentions a strict
    equality between a functor [A ⟶ X] and another inherits the
    identification.  [LeftAdjointLeftInverse] is rejected at the same
    levels, but that rejection does NOT discriminate: its field
    [lali_left : X ⟶ A] is a functor in the REVERSE direction, and the
    functor type alone in that direction is already rejected here --
    [Au ⟶ Xu] is accepted while [Xu ⟶ Au] is not, since [Functor] bounds
    the source hom universe by the target's and the two directions
    together identify them -- so the record's identification is forced
    before its [Adjunction] field (Theory/Adjunction.v, whose own
    block carries [h1 = p1], [h1 = h2], [h1 = p2]) is consulted.  Only
    [Functor_StrictEq_Setoid] is probed in isolation below.

--------
** 6. 可塑性：严格函子相等识别了两个范畴的同态和证明宇宙。

[Functor_StrictEq_Setoid]（Theory/Functor.v）在 [Category@{u1 u4 u4}] 和 [Category@{u2 u4 u4}] 上声明——源和目标只有一个同态级别——因此下面每个提到函子 [A ⟶ X] 与另一个之间严格相等的语句都继承了该识别。[LeftAdjointLeftInverse] 在相同级别下被拒绝，但这种拒绝没有区别：它的字段 [lali_left : X ⟶ A] 是一个反向函子，而在该方向上仅函子类型已经在这里被拒绝——[Au ⟶ Xu] 被接受而 [Xu ⟶ Au] 没有被接受，因为 [Functor] 将源 hom 宇宙限制在目标的宇宙以内，并且两个方向一起确定了它们——因此在查看其 [Adjunction] 字段（Theory/Adjunction.v，其自身块包含 [h1 = p1]、[h1 = h2]、[h1 = p2]）之前，记录的识别被强制执行。下面仅以孤立方式探查 [Functor_StrictEq_Setoid]。
*)

Section UniverseProbe.

Universes ao ah xo xh.
Constraint ah < xh.

Context (Au : Category@{ao ah ah}).
Context (Xu : Category@{xo xh xh}).
Context (Gu : Au ⟶ Xu).

(* control: the functor type, and a functor, at levels declared apart / 控制：函子类型，以及在不同声明级别的函子 *)
Check (Au ⟶ Xu).
Check Gu.
Check (InjectiveOnObjects Gu).

Fail Check (Xu ⟶ Au).
Fail Check (@Functor_StrictEq_Setoid Au Xu).
Fail Check (LeftAdjointLeftInverse Gu).
Fail Check (@lali_along_right_strict Au Xu Gu Gu).
Fail Check (@ffi_implies_ri Au Xu Gu).

End UniverseProbe.

(**
** 7. FORMABILITY: clause (c) identifies the two categories' OBJECT
       universes, and clause (a) does not.

    [ri_iso] compares [A] with [Sub X ri_sub] in [StrictCat], whose
    objects are [Category] at ONE universe instance, so the two must live
    at the same levels -- which is why the packaged
    [lali_characterization] displays [A X : Category@{u6 u13 u13}] where
    [LeftAdjointLeftInverse] alone leaves both object universes free.  The
    controls below are exactly that contrast: at object levels declared
    apart, the functor type and clause (a) are accepted while the
    [StrictCat] isomorphism and (b) => (c) are rejected.

--------
** 7. 可形成性：条款(c)确定了两个类别的对象宇宙，而条款(a)没有。

[ri_iso] 在 [StrictCat] 中比较 [A] 和 [Sub X ri_sub]，其对象在一个宇宙实例中是 [Category]，因此两者必须位于相同的层级——这也是为什么封装的 [lali_characterization] 显示 [A X : Category@{u6 u13 u13}]，而 [LeftAdjointLeftInverse] 单独使用时则让两个对象宇宙保持自由。
下面的控件正是这种对比：在声明为不同对象层级时，函子类型和条款(a) 被接受，而 [StrictCat] 同构和 (b) => (c) 被拒绝。
*)

Section StrictCatObjectProbe.

Universes bo bh co.
Constraint bo < co.

Context (Bu : Category@{bo bh bh}).
Context (Cu2 : Category@{co bh bh}).
Context (Gu2 : Bu ⟶ Cu2).

(* controls: accepted at object levels declared apart *)
Check (Bu ⟶ Cu2).
Check (LeftAdjointLeftInverse Gu2).
Check (@LeftAdjointFFInjective Bu Cu2 Gu2).

Fail Check (@Isomorphism StrictCat Bu Cu2).
Fail Check (@ffi_implies_ri Bu Cu2 Gu2).

End StrictCatObjectProbe.

(**
** 8. FORMABILITY: [Theory/Shapes.v]'s [Point] pins the terminal
       category's hom and proof universes at [Set].

    This is the measured reason the six-line [PointAt] is rebuilt in the
    target instead of consuming [Point]: over a category whose homs are
    declared strictly above [Set], [Point] is not formable while [PointAt]
    is.  The rejection is the donor's minimization, not a restriction on
    the terminal category itself ([_1@{o h p}] has all three levels free);
    it is NOT claimed unavoidable.

--------
** 8. 可形成性：[Theory/Shapes.v] 的 [Point] 固定了终端范畴的同态和证明宇宙在 [Set] 处。

这是六行 [PointAt] 在目标中重建而不是使用 [Point] 的测量原因：在同态严格声明高于 [Set] 的范畴上，[Point] 不可形成，而 [PointAt] 可形成。拒绝是捐赠者的最小化，而不是对终端范畴本身的限制（[_1@{o h p}] 的三个层级都是自由的）；这并不意味着不可避免。
*)

Section PointProbe.

Universes po ph.
Constraint Set < ph.

Context (Cu : Category@{po ph ph}).
Context (c : Cu).

Check (_1@{po ph ph}).
Check (PointAt (C:=Cu) c : _1@{po ph ph} ⟶ Cu).
Check (@terminal_LALI).

Fail Check (Point (C:=Cu) c : _1@{po ph ph} ⟶ Cu).

End PointProbe.

(**
** Non-vacuity of the third leg's hypothesis.

    [lali_image_insertion] inhabits it for every presentation arising
    from a left-adjoint-left-inverse -- Mac Lane's own sentence that the
    insertion has a left-adjoint-left-inverse -- so the conditional leg
    is not an empty statement.

--------
** 第三条假设的非空性。

[lali_image_insertion] 为每个由左伴随-左逆引起的呈现而存在——Mac Lane 自己的句子，即该插入具有一个左伴随-左逆——所以条件分支不是空的陈述。
*)

Check @lali_ri_insertion.
Check @two_LALI.
Check @two_lali_moves_TwoX.
